import streamlit as st
from selenium import webdriver
from selenium.webdriver import Remote, ChromeOptions
from selenium.webdriver.chrome.service import Service
from selenium.webdriver.chromium.remote_connection import ChromiumRemoteConnection
from selenium.webdriver.common.by import By
from selenium.webdriver.support.ui import WebDriverWait
from selenium.webdriver.support import expected_conditions as EC
from webdriver_manager.chrome import ChromeDriverManager
from bs4 import BeautifulSoup, Comment
import time
import pandas as pd
import json
import csv
import io
import random
from tenacity import retry, stop_after_attempt, wait_fixed
import logging
import hashlib
from datetime import datetime, timedelta
import os
from urllib.parse import urljoin, urlparse
import xml.etree.ElementTree as ET
import requests
import schedule
import threading
import re
from PIL import Image
from io import BytesIO
import validators
from ratelimit import limits, sleep_and_retry
from fake_useragent import UserAgent
from urllib.robotparser import RobotFileParser
from concurrent.futures import ThreadPoolExecutor
import aiohttp
import asyncio
import newspaper
from newspaper import Article
import nltk
from dataclasses import dataclass
from typing import Optional, List, Dict
import yaml
import socket
from pathlib import Path

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler('scraper.log'),
        logging.StreamHandler()
    ]
)
logger = logging.getLogger(__name__)

@dataclass
class ScrapingConfig:
    """Configuration for scraping tasks"""
    max_depth: int = 2
    max_pages: int = 100
    respect_robots: bool = True
    follow_links: bool = False
    user_agent: Optional[str] = None
    timeout: int = 30
    max_retries: int = 3
    delay: float = 1.0
    screenshot: bool = False
    save_html: bool = False
    extract_metadata: bool = True
    extract_comments: bool = True
    extract_structured_data: bool = True

@dataclass
class ScrapingResult:
    """Structure for scraping results"""
    url: str
    content: dict
    timestamp: str
    success: bool
    error: Optional[str] = None
    metadata: Optional[dict] = None
    screenshots: Optional[List[str]] = None
    html_path: Optional[str] = None

class ProxyManager:
    def __init__(self):
        self.proxies = []
        self.current_index = 0
        self.proxy_test_url = "http://www.google.com"
        self.test_timeout = 10

    def add_proxy(self, proxy):
        """Add a proxy to the rotation after testing"""
        if not validators.url(proxy):
            return False

        if self.test_proxy(proxy):
            self.proxies.append(proxy)
            return True
        return False

    def test_proxy(self, proxy):
        """Test if proxy is working"""
        try:
            proxies = {
                'http': proxy,
                'https': proxy
            }
            response = requests.get(
                self.proxy_test_url,
                proxies=proxies,
                timeout=self.test_timeout
            )
            return response.status_code == 200
        except:
            return False

    def get_next_proxy(self):
        """Get the next working proxy from the rotation"""
        if not self.proxies:
            return None

        attempts = 0
        while attempts < len(self.proxies):
            proxy = self.proxies[self.current_index]
            self.current_index = (self.current_index + 1) % len(self.proxies)

            if self.test_proxy(proxy):
                return proxy

            attempts += 1

        return None

    def remove_proxy(self, proxy):
        """Remove a proxy from the rotation"""
        if proxy in self.proxies:
            self.proxies.remove(proxy)
            return True
        return False

    def get_working_proxies(self):
        """Get list of currently working proxies"""
        return [proxy for proxy in self.proxies if self.test_proxy(proxy)]

class DataValidator:
    @staticmethod
    def clean_text(text):
        """Clean and normalize text data"""
        if not text:
            return ""
        # Remove extra whitespace
        text = re.sub(r'\s+', ' ', text.strip())
        # Remove special characters but keep basic punctuation
        text = re.sub(r'[^\w\s.,!?-]', '', text)
        return text

    @staticmethod
    def validate_url(url):
        """Validate URL format"""
        return validators.url(url)

    @staticmethod
    def validate_email(email):
        """Validate email format"""
        return validators.email(email)

    @staticmethod
    def clean_html(html):
        """Clean HTML content"""
        soup = BeautifulSoup(html, 'html.parser')
        # Remove script and style elements
        for element in soup(['script', 'style', 'iframe']):
            element.decompose()
        return str(soup)

    @staticmethod
    def sanitize_filename(filename):
        """Sanitize filename for safe saving"""
        return re.sub(r'[^\w\-_.]', '_', filename)

class ContentExtractor:
    """Advanced content extraction capabilities"""

    def __init__(self):
        # Download required NLTK data
        try:
            nltk.data.find('tokenizers/punkt')
        except LookupError:
            nltk.download('punkt')

    def extract_article(self, url: str) -> dict:
        """Extract article content using newspaper3k"""
        try:
            article = Article(url)
            article.download()
            article.parse()
            article.nlp()

            return {
                'title': article.title,
                'text': article.text,
                'summary': article.summary,
                'keywords': article.keywords,
                'authors': article.authors,
                'publish_date': article.publish_date,
                'top_image': article.top_image,
                'images': list(article.images),
                'movies': list(article.movies)
            }
        except Exception as e:
            logger.error(f"Error extracting article content: {str(e)}")
            return {}

    def extract_metadata(self, soup: BeautifulSoup) -> dict:
        """Extract metadata from HTML"""
        metadata = {
            'meta_tags': {},
            'links': {},
            'scripts': [],
            'comments': [],
            'structured_data': []
        }

        # Extract meta tags
        for meta in soup.find_all('meta'):
            name = meta.get('name') or meta.get('property')
            if name:
                metadata['meta_tags'][name] = meta.get('content')

        # Extract links with rel attributes
        for link in soup.find_all('link'):
            rel = link.get('rel')
            if rel:
                metadata['links'][str(rel)] = link.get('href')

        # Extract comments
        metadata['comments'] = [str(comment) for comment in soup.find_all(string=lambda text: isinstance(text, Comment))]

        # Extract JSON-LD structured data
        for script in soup.find_all('script', type='application/ld+json'):
            try:
                metadata['structured_data'].append(json.loads(script.string))
            except:
                continue

        return metadata

class SitemapManager:
    """Enhanced sitemap handling"""

    def __init__(self):
        self.known_sitemaps = set()
        self.sitemap_patterns = [
            "/sitemap.xml",
            "/sitemap_index.xml",
            "/sitemap/",
            "/sitemaps/",
        ]

    async def discover_sitemaps(self, base_url: str) -> List[str]:
        """Discover potential sitemap URLs"""
        discovered = set()

        # Check robots.txt for sitemap
        robots_url = urljoin(base_url, "/robots.txt")
        try:
            async with aiohttp.ClientSession() as session:
                async with session.get(robots_url) as response:
                    if response.status == 200:
                        robots_text = await response.text()
                        for line in robots_text.split('\n'):
                            if line.lower().startswith('sitemap:'):
                                sitemap_url = line.split(':', 1)[1].strip()
                                discovered.add(sitemap_url)
        except Exception as e:
            logger.error(f"Error checking robots.txt: {str(e)}")

        # Check common sitemap patterns
        for pattern in self.sitemap_patterns:
            sitemap_url = urljoin(base_url, pattern)
            discovered.add(sitemap_url)

        return list(discovered)

    async def parse_sitemap(self, url: str) -> List[str]:
        """Parse sitemap and extract URLs"""
        try:
            async with aiohttp.ClientSession() as session:
                async with session.get(url) as response:
                    if response.status == 200:
                        content = await response.text()
                        urls = []

                        # Parse XML content
                        root = ET.fromstring(content)

                        # Handle sitemap index
                        for sitemap in root.findall('.//{http://www.sitemaps.org/schemas/sitemap/0.9}loc'):
                            if sitemap.text.endswith('.xml'):
                                sub_urls = await self.parse_sitemap(sitemap.text)
                                urls.extend(sub_urls)
                            else:
                                urls.append(sitemap.text)

                        return urls
        except Exception as e:
            logger.error(f"Error parsing sitemap {url}: {str(e)}")
            return []

class ScheduleManager:
    def __init__(self):
        self.jobs = {}
        self.running = False
        self.thread = None
        self.results_dir = "scheduled_results"
        Path(self.results_dir).mkdir(exist_ok=True)

    def add_job(self, name, url, content_type, interval_hours):
        """Add a new scheduled scraping job"""
        if name in self.jobs:
            return False

        schedule.every(interval_hours).hours.do(
            self.run_job,
            name=name,
            url=url,
            content_type=content_type
        )
        self.jobs[name] = {
            'url': url,
            'content_type': content_type,
            'interval_hours': interval_hours,
            'last_run': None,
            'next_run': datetime.now() + timedelta(hours=interval_hours),
            'results': []
        }
        return True

    def run_job(self, name, url, content_type):
        """Run a scheduled job"""
        try:
            result = scraper.scrape_website(url, content_type)

            # Save result to file
            timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
            result_file = os.path.join(
                self.results_dir,
                f"{name}_{timestamp}.json"
            )

            with open(result_file, 'w') as f:
                json.dump(result, f, indent=2)

            self.jobs[name]['last_run'] = datetime.now()
            self.jobs[name]['next_run'] = datetime.now() + timedelta(hours=self.jobs[name]['interval_hours'])
            self.jobs[name]['results'].append(result_file)

            # Keep only last 10 results
            if len(self.jobs[name]['results']) > 10:
                old_result = self.jobs[name]['results'].pop(0)
                if os.path.exists(old_result):
                    os.remove(old_result)

            return result
        except Exception as e:
            logger.error(f"Scheduled job {name} failed: {str(e)}")
            return None

    def start(self):
        """Start the scheduler"""
        if not self.running:
            self.running = True
            self.thread = threading.Thread(target=self._run_continuously)
            self.thread.daemon = True
            self.thread.start()

    def stop(self):
        """Stop the scheduler"""
        self.running = False
        if self.thread:
            self.thread.join()
            self.thread = None

    def _run_continuously(self):
        while self.running:
            schedule.run_pending()
            time.sleep(60)

    def get_job_status(self, name):
        """Get the status of a specific job"""
        if name in self.jobs:
            return self.jobs[name]
        return None

    def get_all_jobs(self):
        """Get status of all jobs"""
        return {
            name: {
                'url': job['url'],
                'content_type': job['content_type'],
                'interval_hours': job['interval_hours'],
                'last_run': job['last_run'],
                'next_run': job['next_run'],
                'result_count': len(job['results'])
            }
            for name, job in self.jobs.items()
        }

class WebScraper:
    def __init__(self):
        self.session_data = {}
        self.history = []
        self.proxy_manager = ProxyManager()
        self.schedule_manager = ScheduleManager()
        self.data_validator = DataValidator()
        self.content_extractor = ContentExtractor()
        self.sitemap_manager = SitemapManager()
        self.config = ScrapingConfig()
        self.user_agent = UserAgent()
        self.rate_limit = 60  # requests per minute

    def load_config(self, config_file: str):
        """Load scraping configuration from YAML file"""
        try:
            with open(config_file, 'r') as f:
                config_data = yaml.safe_load(f)
                self.config = ScrapingConfig(**config_data)
        except Exception as e:
            logger.error(f"Error loading config: {str(e)}")

    def save_config(self, config_file: str):
        """Save current configuration to YAML file"""
        try:
            with open(config_file, 'w') as f:
                yaml.dump(self.config.__dict__, f)
        except Exception as e:
            logger.error(f"Error saving config: {str(e)}")

    def check_robots_txt(self, url: str) -> bool:
        """Check if scraping is allowed by robots.txt"""
        if not self.config.respect_robots:
            return True

        try:
            parsed_url = urlparse(url)
            robots_url = f"{parsed_url.scheme}://{parsed_url.netloc}/robots.txt"
            rp = RobotFileParser()
            rp.set_url(robots_url)
            rp.read()
            return rp.can_fetch(self.config.user_agent or self.user_agent.random, url)
        except Exception as e:
            logger.error(f"Error checking robots.txt: {str(e)}")
            return True

    def get_chrome_driver(self):
        """Get configured Chrome WebDriver instance"""
        chrome_options =   ChromeOptions()
        chrome_options.add_argument('--no-sandbox')
        chrome_options.add_argument('--headless')
        chrome_options.add_argument('--disable-dev-shm-usage')

        if self.config.user_agent:
            chrome_options.add_argument(f'--user-agent={self.config.user_agent}')
        else:
            chrome_options.add_argument(f'--user-agent={self.user_agent.random}')

        # Add proxy if available
        proxy = self.proxy_manager.get_next_proxy()
        if proxy:
            chrome_options.add_argument(f'--proxy-server={proxy}')

        service = Service(ChromeDriverManager().install())
        return webdriver.Chrome(service=service, options=chrome_options)

    def scrape_webform(self, driver, form_selector):
        """Scrape data from a webform"""
        try:
            form = WebDriverWait(driver, 10).until(
                EC.presence_of_element_located((By.CSS_SELECTOR, form_selector))
            )

            # Extract form data
            inputs = form.find_elements(By.CSS_SELECTOR, 'input, select, textarea')
            form_data = {}

            for input_element in inputs:
                name = input_element.get_attribute('name')
                if name:
                    form_data[name] = {
                        'type': input_element.get_attribute('type'),
                        'value': input_element.get_attribute('value'),
                        'placeholder': input_element.get_attribute('placeholder')
                    }

            return form_data
        except Exception as e:
            logger.error(f"Error scraping webform: {str(e)}")
            return None

    @sleep_and_retry
    @limits(calls=60, period=60)
    def rate_limited_request(self, url):
        """Make a rate-limited request"""
        return requests.get(url)

    def capture_screenshot(self, driver, url):
        """Capture a screenshot of the page"""
        try:
            screenshot = driver.get_screenshot_as_png()
            image = Image.open(BytesIO(screenshot))
            timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
            filename = f"screenshots/{urlparse(url).netloc}_{timestamp}.png"
            os.makedirs('screenshots', exist_ok=True)
            image.save(filename)
            return filename
        except Exception as e:
            logger.error(f"Screenshot capture failed: {str(e)}")
            return None

    async def async_scrape(self, urls: List[str]) -> List[ScrapingResult]:
        """Scrape multiple URLs asynchronously"""
        async def scrape_single(url: str) -> ScrapingResult:
            try:
                if not self.check_robots_txt(url):
                    return ScrapingResult(
                        url=url,
                        content={},
                        timestamp=datetime.now().isoformat(),
                        success=False,
                        error="Blocked by robots.txt"
                    )

                async with aiohttp.ClientSession() as session:
                    async with session.get(
                            url,
                            headers={'User-Agent': self.config.user_agent or self.user_agent.random}
                    ) as response:
                        html = await response.text()
                        soup = BeautifulSoup(html, 'html.parser')

                        # Extract various types of content
                        article_content = self.content_extractor.extract_article(url)
                        metadata = self.content_extractor.extract_metadata(soup)

                        return ScrapingResult(
                            url=url,
                            content={
                                'article': article_content,
                                'metadata': metadata
                            },
                            timestamp=datetime.now().isoformat(),
                            success=True
                        )
            except Exception as e:
                return ScrapingResult(
                    url=url,
                    content={},
                    timestamp=datetime.now().isoformat(),
                    success=False,
                    error=str(e)
                )

        tasks = [scrape_single(url) for url in urls]
        results = await asyncio.gather(*tasks)
        return results

    def scrape_website(self, url, content_type, form_selector=None, login_required=False, login_details=None):
        """Main scraping function"""
        progress_bar = st.progress(0)
        status_text = st.empty()

        # Validate URL
        if not self.data_validator.validate_url(url):
            raise ValueError("Invalid URL format")

        # Check robots.txt
        if not self.check_robots_txt(url):
            raise ValueError("Scraping not allowed by robots.txt")

        # Check cache first
        cached_content = self.load_from_cache(url)
        if cached_content and not login_required:
            status_text.text("Loading from cache...")
            return cached_content

        status_text.text("Initializing Chrome WebDriver...")
        progress_bar.progress(10)

        driver = self.get_chrome_driver()

        try:
            if login_required and login_details:
                status_text.text("Attempting login...")
                login_success = self.handle_login(
                    driver,
                    login_details['login_url'],
                    login_details['username_selector'],
                    login_details['password_selector'],
                    login_details['submit_selector'],
                    login_details['username'],
                    login_details['password']
                )
                if not login_success:
                    raise Exception("Login failed")

            status_text.text(f"Connected! Navigating to {url}...")
            progress_bar.progress(30)

            driver.get(url)
            time.sleep(random.uniform(1, 3))  # Random delay
            html = driver.page_source

            status_text.text('Page loaded. Scraping content...')
            progress_bar.progress(50)

            # Initialize result dictionary
            result = {
                'url': url,
                'timestamp': datetime.now().isoformat(),
                'content_type': content_type,
                'data': None,
                'metadata': None,
                'screenshots': [],
                'html_path': None
            }

            # Capture screenshot if enabled
            if self.config.screenshot:
                screenshot_path = self.capture_screenshot(driver, url)
                if screenshot_path:
                    result['screenshots'].append(screenshot_path)

            # Save HTML if enabled
            if self.config.save_html:
                html_dir = "saved_html"
                os.makedirs(html_dir, exist_ok=True)
                html_path = os.path.join(
                    html_dir,
                    f"{self.data_validator.sanitize_filename(urlparse(url).netloc)}_{datetime.now().strftime('%Y%m%d_%H%M%S')}.html"
                )
                with open(html_path, 'w', encoding='utf-8') as f:
                    f.write(html)
                result['html_path'] = html_path

            # Extract content based on type
            if content_type == 'webform':
                result['data'] = self.scrape_webform(driver, form_selector)
            else:
                soup = BeautifulSoup(html, 'html.parser')

                if content_type == 'text':
                    result['data'] = soup.get_text(separator='\n', strip=True)
                elif content_type == 'links':
                    result['data'] = [{'text': a.text, 'href': a.get('href')} for a in soup.find_all('a', href=True)]
                elif content_type == 'images':
                    result['data'] = [{'alt': img.get('alt', ''), 'src': img.get('src')} for img in soup.find_all('img', src=True)]
                elif content_type == 'tables':
                    tables = soup.find_all('table')
                    result['data'] = [pd.read_html(str(table))[0].to_dict('records') for table in tables]
                elif content_type == 'dynamic':
                    time.sleep(5)
                    result['data'] = self.extract_dynamic_content(driver)
                elif content_type == 'article':
                    result['data'] = self.content_extractor.extract_article(url)

            # Extract metadata if enabled
            if self.config.extract_metadata:
                result['metadata'] = self.content_extractor.extract_metadata(soup)

            # Save to cache if successful
            if not login_required:
                self.save_to_cache(url, result)

            # Add to history
            self.history.append({
                'url': url,
                'timestamp': datetime.now().isoformat(),
                'content_type': content_type,
                'success': True
            })

            progress_bar.progress(100)
            status_text.text('Scraping completed!')

            return result

        except Exception as e:
            logger.error(f"Error during scraping: {str(e)}")
            self.history.append({
                'url': url,
                'timestamp': datetime.now().isoformat(),
                'content_type': content_type,
                'success': False,
                'error': str(e)
            })
            raise e
        finally:
            driver.quit()

    def extract_dynamic_content(self, driver):
        """Extract dynamically loaded content"""
        try:
            dynamic_elements = WebDriverWait(driver, 10).until(
                EC.presence_of_all_elements_located((By.CSS_SELECTOR, '[data-dynamic]'))
            )
            return [elem.text for elem in dynamic_elements]
        except Exception as e:
            logger.error(f"Error extracting dynamic content: {str(e)}")
            return []

    def get_scraping_history(self):
        """Get scraping history"""
        return self.history

    def handle_login(self, driver, login_url, username_selector, password_selector, submit_selector, username, password):
        """Handle login process"""
        try:
            driver.get(login_url)
            username_field = WebDriverWait(driver, 10).until(
                EC.presence_of_element_located((By.CSS_SELECTOR, username_selector))
            )
            password_field = WebDriverWait(driver, 10).until(
                EC.presence_of_element_located((By.CSS_SELECTOR, password_selector))
            )
            submit_button = WebDriverWait(driver, 10).until(
                EC.presence_of_element_located((By.CSS_SELECTOR, submit_selector))
            )

            username_field.send_keys(username)
            password_field.send_keys(password)
            submit_button.click()

            time.sleep(3)  # Wait for login to complete
            return True
        except Exception as e:
            logger.error(f"Login failed: {str(e)}")
            return False

    def save_to_cache(self, url, content):
        """Save scraped content to cache"""
        cache_dir = "scraper_cache"
        if not os.path.exists(cache_dir):
            os.makedirs(cache_dir)

        url_hash = hashlib.md5(url.encode()).hexdigest()
        cache_file = os.path.join(cache_dir, f"{url_hash}.json")

        cache_data = {
            "url": url,
            "content": content,
            "timestamp": datetime.now().isoformat()
        }

        with open(cache_file, 'w') as f:
            json.dump(cache_data, f, indent=2)

    def load_from_cache(self, url, max_age_hours=24):
        """Load content from cache if available and not expired"""
        cache_dir = "scraper_cache"
        url_hash = hashlib.md5(url.encode()).hexdigest()
        cache_file = os.path.join(cache_dir, f"{url_hash}.json")

        if os.path.exists(cache_file):
            with open(cache_file, 'r') as f:
                cache_data = json.load(f)

            cached_time = datetime.fromisoformat(cache_data["timestamp"])
            age = datetime.now() - cached_time

            if age.total_seconds() < max_age_hours * 3600:
                return cache_data["content"]
        return None

def export_data(data, format):
    """Export data in various formats"""
    if format == 'json':
        return json.dumps(data, indent=2)
    elif format == 'csv':
        if isinstance(data, (list, dict)):
            if isinstance(data, dict):
                data = [data]
            output = io.StringIO()
            if data:
                writer = csv.DictWriter(output, fieldnames=data[0].keys())
                writer.writeheader()
                writer.writerows(data)
            return output.getvalue()
        else:
            return "Data not suitable for CSV export"
    elif format == 'txt':
        if isinstance(data, str):
            return data
        else:
            return str(data)

# Initialize the scraper
scraper = WebScraper()

# Streamlit UI
st.title("Advanced Web Scraper")
st.write("This tool scrapes websites and webforms with advanced features like authentication and caching.")

# Sidebar for advanced options
with st.sidebar:
    st.header("Advanced Options")

    # Configuration
    st.subheader("Scraping Configuration")
    max_depth = st.slider("Max Crawl Depth", 1, 10, 2)
    max_pages = st.number_input("Max Pages to Scrape", 1, 1000, 100)
    respect_robots = st.checkbox("Respect robots.txt", value=True)
    follow_links = st.checkbox("Follow Links", value=False)
    enable_cache = st.checkbox("Enable Caching", value=True)
    cache_duration = st.slider("Cache Duration (hours)", 1, 72, 24)

    # Save/Load Configuration
    st.subheader("Configuration Management")
    config_file = st.text_input("Configuration File", value="scraper_config.yaml")
    col1, col2 = st.columns(2)
    with col1:
        if st.button("Save Config"):
            scraper.config = ScrapingConfig(
                max_depth=max_depth,
                max_pages=max_pages,
                respect_robots=respect_robots,
                follow_links=follow_links
            )
            scraper.save_config(config_file)
            st.success("Configuration saved!")
    with col2:
        if st.button("Load Config"):
            scraper.load_config(config_file)
            st.success("Configuration loaded!")

    st.header("Authentication")
    login_required = st.checkbox("Login Required")

    login_details = None
    if login_required:
        login_url = st.text_input("Login URL")
        username = st.text_input("Username")
        password = st.text_input("Password", type="password")
        username_selector = st.text_input("Username Field Selector", value="#username")
        password_selector = st.text_input("Password Field Selector", value="#password")
        submit_selector = st.text_input("Submit Button Selector", value="button[type='submit']")

        login_details = {
            'login_url': login_url,
            'username_selector': username_selector,
            'password_selector': password_selector,
            'submit_selector': submit_selector,
            'username': username,
            'password': password
        }

    # Proxy Management
    st.header("Proxy Management")
    if st.checkbox("Enable Proxy"):
        proxy = st.text_input("Add Proxy (format: http://ip:port)")
        if st.button("Add Proxy"):
            if scraper.proxy_manager.add_proxy(proxy):
                st.success("Proxy added successfully!")
            else:
                st.error("Invalid proxy format or proxy not working")

        working_proxies = scraper.proxy_manager.get_working_proxies()
        if working_proxies:
            st.write("Working Proxies:")
            for proxy in working_proxies:
                st.code(proxy)

    # Scheduling
    st.header("Scheduling")
    if st.checkbox("Enable Scheduling"):
        schedule_name = st.text_input("Job Name")
        schedule_interval = st.number_input("Interval (hours)", min_value=1, value=24)
        schedule_url = st.text_input("URL to scrape")
        schedule_content_type = st.selectbox(
            "Content type to scrape",
            ['text', 'links', 'images', 'tables', 'webform', 'dynamic', 'article']
        )
        if st.button("Schedule Job"):
            if schedule_name and schedule_url:
                if scraper.schedule_manager.add_job(schedule_name, schedule_url, schedule_content_type, schedule_interval):
                    st.success("Job scheduled successfully!")
                else:
                    st.error("Job name already exists")
            else:
                st.error("Please provide both job name and URL")

        # Show scheduled jobs
        jobs = scraper.schedule_manager.get_all_jobs()
        if jobs:
            st.write("Scheduled Jobs:")
            for name, job in jobs.items():
                with st.expander(f"Job: {name}"):
                    st.write(f"URL: {job['url']}")
                    st.write(f"Type: {job['content_type']}")
                    st.write(f"Interval: {job['interval_hours']} hours")
                    if job['last_run']:
                        st.write(f"Last Run: {job['last_run']}")
                    if job['next_run']:
                        st.write(f"Next Run: {job['next_run']}")
                    st.write(f"Results: {job['result_count']}")

    # Batch Scraping
    st.header("Batch Scraping")
    batch_urls = st.text_area("Enter URLs (one per line)")
    if st.button("Scrape Batch"):
        urls = [url.strip() for url in batch_urls.split('\n') if url.strip()]
        if urls:
            results = asyncio.run(scraper.async_scrape(urls))
            st.session_state['batch_results'] = results
            st.success(f"Scraped {len(results)} URLs!")

# Main content
url = st.text_input("Enter a Website URL to Scrape")
content_type = st.selectbox(
    "Select content to scrape",
    ['text', 'links', 'images', 'tables', 'webform', 'dynamic', 'article']
)

form_selector = None
if content_type == 'webform':
    form_selector = st.text_input("Enter the CSS selector for the form (e.g., '#contact-form')")

if st.button("Scrape Site"):
    if url:
        try:
            with st.spinner(f"Scraping {content_type} from: {url}"):
                result = scraper.scrape_website(
                    url,
                    content_type,
                    form_selector,
                    login_required,
                    login_details
                )

                st.subheader(f"Scraped {content_type.capitalize()}:")
                if content_type == 'text':
                    st.text_area("", result['data'], height=300)
                else:
                    st.json(result)

                # Show screenshots if available
                if result.get('screenshots'):
                    st.subheader("Screenshots:")
                    for screenshot in result['screenshots']:
                        st.image(screenshot)

                # Show metadata if available
                if result.get('metadata'):
                    with st.expander("Metadata"):
                        st.json(result['metadata'])

                # Export options
                export_format = st.selectbox("Select export format", ['json', 'csv', 'txt'])
                exported_data = export_data(result, export_format)
                st.download_button(
                    label=f"Download as {export_format.upper()}",
                    data=exported_data,
                    file_name=f"scraped_data.{export_format}",
                    mime=f"text/{export_format}"
                )

                # Show scraping history
                if st.checkbox("Show Scraping History"):
                    st.subheader("Scraping History")
                    history_df = pd.DataFrame(scraper.get_scraping_history())
                    st.dataframe(history_df)

        except Exception as e:
            st.error(f"An error occurred: {str(e)}")
    else:
        st.warning("Please enter a URL to scrape.")

# Show batch results if available
if 'batch_results' in st.session_state:
    st.header("Batch Scraping Results")
    for result in st.session_state['batch_results']:
        with st.expander(f"Result for {result.url}"):
            st.json(result.__dict__)



# Start the scheduler if it's not running
if not scraper.schedule_manager.running:
    scraper.schedule_manager.start()